import os
import re
import json
import time
import ipaddress
import hashlib
import base64
import socket
import sqlite3
import concurrent.futures
from datetime import datetime, timedelta
from urllib.parse import urlparse, parse_qs, unquote
from typing import Optional, Dict, List, Tuple, Any, Set
import requests
import geoip2.database
import geoip2.errors
from cryptography.fernet import Fernet
import ssl
import OpenSSL

try:
    import ip2location
    IP2LOCATION_AVAILABLE = True
except ImportError:
    IP2LOCATION_AVAILABLE = False

class IPValidator:
    @staticmethod
    def is_valid_ip(ip: str) -> bool:
        try:
            ipaddress.ip_address(ip)
            return True
        except ValueError:
            return False
    
    @staticmethod
    def normalize_ip(ip: str) -> str:
        if not ip:
            return ip
        ip = str(ip).strip().lower()
        ip = re.sub(r'^https?://', '', ip)
        if ':' in ip and not ip.startswith('['):
            parts = ip.split(':')
            if len(parts) > 4:
                return ip
            elif len(parts) == 2 and parts[1].isdigit():
                return parts[0]
        return ip
    
    @staticmethod
    def extract_ip_from_string(text: str) -> Optional[str]:
        ip_patterns = [
            r'\b(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b',
            r'\b(?:[A-F0-9]{1,4}:){7}[A-F0-9]{1,4}\b',
            r'\[([0-9a-fA-F:]+)\]'
        ]
        for pattern in ip_patterns:
            matches = re.findall(pattern, text)
            if matches:
                return matches[0]
        return None
    
    @staticmethod
    def resolve_domain_to_ips(domain: str) -> List[str]:
        ips = []
        try:
            for family in (socket.AF_INET, socket.AF_INET6):
                try:
                    results = socket.getaddrinfo(domain, None, family=family, proto=socket.IPPROTO_TCP)
                    for res in results:
                        if res[4]:
                            ip = res[4][0]
                            if ip not in ips and IPValidator.is_valid_ip(ip):
                                ips.append(ip)
                except (socket.gaierror, socket.timeout, OSError):
                    continue
        except:
            pass
        return ips

class CacheManager:
    def __init__(self, max_size: int = 50000, ttl_hours: int = 24):
        self.max_size = max_size
        self.ttl = ttl_hours * 3600
        self.db_path = 'cache.db'
        self.init_db()
    
    def init_db(self):
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS ip_cache (
                ip TEXT PRIMARY KEY,
                country TEXT,
                source TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                expires_at TIMESTAMP
            )
        ''')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_expires ON ip_cache(expires_at)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_created ON ip_cache(created_at)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_ip ON ip_cache(ip)')
        conn.commit()
        conn.close()
    
    def get(self, ip: str) -> Optional[Tuple[str, str]]:
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        cursor.execute('''
            SELECT country, source FROM ip_cache 
            WHERE ip = ? AND (expires_at IS NULL OR expires_at > datetime('now'))
        ''', (ip,))
        result = cursor.fetchone()
        conn.close()
        return result if result else None
    
    def set(self, ip: str, country: str, source: str = "local"):
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        expires_at = datetime.now() + timedelta(seconds=self.ttl)
        cursor.execute('''
            INSERT OR REPLACE INTO ip_cache (ip, country, source, expires_at)
            VALUES (?, ?, ?, ?)
        ''', (ip, country, source, expires_at))
        conn.commit()
        conn.close()
    
    def cleanup(self):
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        cursor.execute('DELETE FROM ip_cache WHERE expires_at < datetime("now")')
        cursor.execute('''
            DELETE FROM ip_cache WHERE rowid IN (
                SELECT rowid FROM ip_cache ORDER BY created_at DESC LIMIT -1 OFFSET ?
            )
        ''', (self.max_size,))
        conn.commit()
        conn.close()

class EncryptedStorage:
    def __init__(self, key_file: str = 'storage.key'):
        self.key_file = key_file
        self.key = self.load_or_generate_key()
        self.cipher = Fernet(self.key)
    
    def load_or_generate_key(self) -> bytes:
        if os.path.exists(self.key_file):
            with open(self.key_file, 'rb') as f:
                return f.read()
        key = Fernet.generate_key()
        with open(self.key_file, 'wb') as f:
            f.write(key)
        return key
    
    def encrypt(self, data: str) -> bytes:
        return self.cipher.encrypt(data.encode('utf-8'))
    
    def decrypt(self, encrypted_data: bytes) -> str:
        return self.cipher.decrypt(encrypted_data).decode('utf-8')
    
    def save_encrypted(self, data: str, filename: str):
        encrypted = self.encrypt(data)
        with open(filename, 'wb') as f:
            f.write(encrypted)
    
    def load_encrypted(self, filename: str) -> Optional[str]:
        if not os.path.exists(filename):
            return None
        try:
            with open(filename, 'rb') as f:
                encrypted = f.read()
            return self.decrypt(encrypted)
        except:
            return None

class TLSInspector:
    @staticmethod
    def extract_certificate_info(hostname: str, port: int = 443, timeout: int = 3) -> Optional[Dict]:
        try:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            
            with socket.create_connection((hostname, port), timeout=timeout) as sock:
                with context.wrap_socket(sock, server_hostname=hostname) as ssock:
                    cert_bin = ssock.getpeercert(binary_form=True)
                    if cert_bin:
                        x509 = OpenSSL.crypto.load_certificate(OpenSSL.crypto.FILETYPE_ASN1, cert_bin)
                        return TLSInspector.parse_certificate(x509)
        except:
            pass
        return None
    
    @staticmethod
    def parse_certificate(x509) -> Dict:
        info = {}
        try:
            subject = x509.get_subject()
            info['common_name'] = subject.CN if hasattr(subject, 'CN') else None
            
            issuer = x509.get_issuer()
            info['issuer'] = issuer.CN if hasattr(issuer, 'CN') else None
            
            san = ''
            for i in range(x509.get_extension_count()):
                ext = x509.get_extension(i)
                if 'subjectAltName' in str(ext.get_short_name()):
                    san = str(ext)
                    break
            info['san'] = san
            
            info['not_before'] = x509.get_notBefore().decode('utf-8') if x509.get_notBefore() else None
            info['not_after'] = x509.get_notAfter().decode('utf-8') if x509.get_notAfter() else None
            
            info['serial'] = str(x509.get_serial_number())
            info['signature_algorithm'] = x509.get_signature_algorithm().decode('utf-8') if x509.get_signature_algorithm() else None
        except:
            pass
        return info

class ConfigIPExtractor:
    def __init__(self):
        self.cdn_keywords = [
            'cdn.cloudflare',
            'cloudfront',
            'fastly',
            'akamai',
            'edgecast',
            'cachefly',
            'incapdns',
            'stackpath',
            'googleusercontent',
            'amazonaws',
            'azureedge',
            'keycdn',
            'azion',
            'imperva',
            'myracloud',
            'belugacdn',
            'cdn77',
            'cf-ipfs',
            'hwcdn',
            'cdngc',
            'cdngs',
            'gcdn'
        ]
        
        self.cdn_ranges = [
            ipaddress.ip_network('104.16.0.0/12'),
            ipaddress.ip_network('172.64.0.0/13'),
            ipaddress.ip_network('131.0.72.0/22'),
        ]
    
    def is_cdn_domain(self, domain: str) -> bool:
        if not domain:
            return False
        domain_lower = domain.lower()
        for keyword in self.cdn_keywords:
            if keyword in domain_lower:
                return True
        return False
    
    def is_cdn_ip(self, ip: str) -> bool:
        try:
            ip_obj = ipaddress.ip_address(ip)
            for cidr in self.cdn_ranges:
                if ip_obj in cidr:
                    return True
        except (ValueError, ipaddress.AddressValueError):
            pass
        return False
    
    def extract_from_sni(self, config_str: str) -> Optional[str]:
        sni_patterns = [
            r'sni=([^&\s]+)',
            r'peer=([^&\s]+)',
            r'host=([^&\s]+)',
            r'serverName=([^&\s]+)'
        ]
        for pattern in sni_patterns:
            match = re.search(pattern, config_str, re.IGNORECASE)
            if match:
                host = unquote(match.group(1))
                if host and '.' in host and len(host) > 3:
                    return host
        return None
    
    def extract_server_from_config(self, config_str: str) -> Optional[str]:
        try:
            config_str = config_str.strip()
            if not config_str:
                return None
            
            if config_str.startswith('vmess://'):
                config_str = config_str[8:]
                padding = (-len(config_str) % 4)
                if padding:
                    config_str += '=' * padding
                try:
                    decoded = json.loads(base64.b64decode(config_str).decode('utf-8'))
                    server = decoded.get('add', '')
                    if server:
                        return server
                except:
                    return None
            
            elif config_str.startswith('vless://'):
                parts = config_str[8:].split('?', 1)
                if '@' in parts[0]:
                    server_part = parts[0].split('@')[1]
                    server = server_part.split(':')[0]
                    if server:
                        return server
            
            elif config_str.startswith('trojan://'):
                config_str = config_str[9:]
                if '#' in config_str:
                    config_str = config_str.split('#')[0]
                if '@' in config_str:
                    server = config_str.split('@')[1].split(':')[0]
                    if server:
                        return server
            
            elif config_str.startswith('ss://'):
                try:
                    if '@' in config_str:
                        parts = config_str[5:].split('#')[0]
                        server = parts.split('@')[1].split(':')[0]
                        if server:
                            return server
                    else:
                        encoded_part = config_str[5:].split('#')[0]
                        if '?' in encoded_part:
                            encoded_part = encoded_part.split('?')[0]
                        padding = (-len(encoded_part) % 4)
                        if padding:
                            encoded_part += '=' * padding
                        decoded = base64.b64decode(encoded_part).decode('utf-8', errors='ignore')
                        if '@' in decoded:
                            server = decoded.split('@')[1].split(':')[0]
                            if server:
                                return server
                except:
                    pass
            
            elif config_str.startswith('hysteria://') or config_str.startswith('hysteria2://') or config_str.startswith('hy2://'):
                try:
                    server_part = config_str.split('://')[1].split('?')[0]
                    server = server_part.split(':')[0]
                    if server:
                        return server
                except:
                    pass
            
            elif config_str.startswith('tuic://'):
                try:
                    server_part = config_str[7:].split('?')[0]
                    server = server_part.split(':')[0]
                    if server:
                        return server
                except:
                    pass
            
        except Exception:
            pass
        
        return None

class CountryClassifier:
    def __init__(self, max_workers: int = 10):
        self.max_workers = max_workers
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
        self.cache_manager = CacheManager(max_size=50000)
        self.extractor = ConfigIPExtractor()
        self.validator = IPValidator()
        
        self.database_paths = {
            'dbip': 'databases/dbip.mmdb',
            'asn': 'databases/asn.mmdb',
        }
        
        self.geoip_readers: Dict[str, Any] = {}
        
        self.setup_databases()
        self.init_readers()
    
    def setup_databases(self):
        os.makedirs('databases', exist_ok=True)
        
        if not os.path.exists(self.database_paths['dbip']):
            print("دانلود دیتابیس DB-IP...")
            self.download_dbip_database()
    
    def download_dbip_database(self):
        try:
            import gzip
            import shutil
            
            url = 'https://download.db-ip.com/free/dbip-city-lite-latest.mmdb.gz'
            response = self.session.get(url, stream=True, timeout=60)
            response.raise_for_status()
            
            temp_file = self.database_paths['dbip'] + '.gz'
            with open(temp_file, 'wb') as f:
                for chunk in response.iter_content(chunk_size=8192):
                    f.write(chunk)
            
            with gzip.open(temp_file, 'rb') as f_in:
                with open(self.database_paths['dbip'], 'wb') as f_out:
                    shutil.copyfileobj(f_in, f_out)
            
            os.remove(temp_file)
            print(f"دیتابیس DB-IP دانلود شد: {self.database_paths['dbip']}")
            
        except Exception as e:
            print(f"خطا در دانلود دیتابیس DB-IP: {e}")
            print("استفاده از APIهای آنلاین...")
    
    def init_readers(self):
        try:
            if os.path.exists(self.database_paths['dbip']):
                self.geoip_readers['dbip'] = geoip2.database.Reader(self.database_paths['dbip'])
                print("DB-IP Reader راه‌اندازی شد")
        except Exception as e:
            print(f"خطا در راه‌اندازی DB-IP Reader: {e}")
    
    def resolve_domain_to_ip(self, domain: str) -> Optional[str]:
        try:
            ips = self.validator.resolve_domain_to_ips(domain)
            if not ips:
                return None
            
            for ip in ips:
                if ip and self.validator.is_valid_ip(ip):
                    return ip
            
            return ips[0] if ips else None
            
        except Exception:
            return None
    
    def get_country_from_ip_local(self, ip: str) -> Optional[str]:
        try:
            if not self.validator.is_valid_ip(ip):
                return None
            
            cached = self.cache_manager.get(ip)
            if cached:
                country, source = cached
                return country
            
            if self.extractor.is_cdn_ip(ip):
                return None
            
            country = None
            
            if 'dbip' in self.geoip_readers:
                try:
                    response = self.geoip_readers['dbip'].city(ip)
                    if response and response.country and response.country.iso_code:
                        country = response.country.iso_code
                        self.cache_manager.set(ip, country, "dbip")
                        return country
                except (geoip2.errors.AddressNotFoundError, AttributeError):
                    pass
            
            return country
            
        except Exception:
            return None
    
    def get_country_from_ip_api(self, ip: str) -> Optional[str]:
        apis = [
            {'url': f'http://ip-api.com/json/{ip}?fields=status,countryCode', 'field': 'countryCode'},
            {'url': f'https://api.country.is/{ip}', 'field': 'country'},
        ]
        
        for api in apis:
            try:
                time.sleep(0.2)
                response = self.session.get(api['url'], timeout=5)
                if response.status_code == 200:
                    data = response.json()
                    if api['url'].startswith('http://ip-api.com'):
                        if data.get('status') == 'success':
                            country = data.get(api['field'])
                            if country and country != 'undefined':
                                self.cache_manager.set(ip, country, "ip-api")
                                return country
                    else:
                        country = data.get(api['field'])
                        if country and country != 'undefined':
                            self.cache_manager.set(ip, country, "country.is")
                            return country
            except:
                continue
        
        return None
    
    def verify_country_with_multiple_sources(self, ip: str) -> Optional[str]:
        sources = []
        
        local_country = self.get_country_from_ip_local(ip)
        if local_country:
            sources.append(local_country)
        
        api_country = self.get_country_from_ip_api(ip)
        if api_country:
            sources.append(api_country)
        
        if not sources:
            return None
        
        if len(sources) == 1:
            return sources[0]
        
        if len(set(sources)) == 1:
            return sources[0]
        
        country_counts = {}
        for country in sources:
            country_counts[country] = country_counts.get(country, 0) + 1
        
        majority_country = max(country_counts.items(), key=lambda x: x[1])[0]
        return majority_country
    
    def get_country_for_config(self, config_str: str) -> Optional[str]:
        try:
            server = self.extractor.extract_server_from_config(config_str)
            if not server:
                return None
            
            if self.validator.is_valid_ip(server):
                ip = server
            else:
                if self.extractor.is_cdn_domain(server):
                    sni = self.extractor.extract_from_sni(config_str)
                    if sni and not self.extractor.is_cdn_domain(sni):
                        server = sni
                
                ip = self.resolve_domain_to_ip(server)
                if not ip:
                    return None
            
            if not ip or self.extractor.is_cdn_ip(ip):
                return None
            
            country = self.verify_country_with_multiple_sources(ip)
            return country
            
        except Exception:
            return None
    
    def get_config_type(self, config_str: str) -> str:
        if config_str.startswith('vmess://'):
            return 'vmess'
        elif config_str.startswith('vless://'):
            return 'vless'
        elif config_str.startswith('trojan://'):
            return 'trojan'
        elif config_str.startswith('ss://'):
            return 'ss'
        elif config_str.startswith('hysteria2://') or config_str.startswith('hy2://'):
            return 'hysteria2'
        elif config_str.startswith('hysteria://'):
            return 'hysteria'
        elif config_str.startswith('tuic://'):
            return 'tuic'
        elif config_str.startswith('wireguard://'):
            return 'wireguard'
        else:
            return 'other'
    
    def process_config(self, config_str: str) -> Dict[str, Any]:
        try:
            country = self.get_country_for_config(config_str)
            config_type = self.get_config_type(config_str)
            
            if not country:
                country = 'UNKNOWN'
            
            config_hash = hashlib.sha256(config_str.encode()).hexdigest()
            
            return {
                'config': config_str,
                'country': country,
                'type': config_type,
                'hash': config_hash[:16]
            }
        except Exception as e:
            return {
                'config': config_str,
                'country': 'UNKNOWN',
                'type': 'other',
                'hash': hashlib.sha256(config_str.encode()).hexdigest()[:16],
                'error': str(e)
            }
    
    def classify_configs(self, configs: List[str]) -> Dict[str, Any]:
        print(f"در حال پردازش {len(configs)} کانفیگ...")
        
        results = {
            'by_country': {},
            'by_type': {},
            'unknown': [],
            'failed': 0
        }
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = {executor.submit(self.process_config, config): config for config in configs}
            
            completed = 0
            for future in concurrent.futures.as_completed(futures):
                try:
                    result = future.result(timeout=15)
                    completed += 1
                    
                    if completed % 100 == 0:
                        print(f"پردازش شده: {completed}/{len(configs)}")
                    
                    country = result['country']
                    config_type = result['type']
                    
                    if country == 'UNKNOWN':
                        results['unknown'].append(result['config'])
                        continue
                    
                    if country not in results['by_country']:
                        results['by_country'][country] = {'all': [], 'by_type': {}}
                    
                    results['by_country'][country]['all'].append(result['config'])
                    
                    if config_type not in results['by_country'][country]['by_type']:
                        results['by_country'][country]['by_type'][config_type] = []
                    
                    results['by_country'][country]['by_type'][config_type].append(result['config'])
                    
                    if config_type not in results['by_type']:
                        results['by_type'][config_type] = {}
                    
                    if country not in results['by_type'][config_type]:
                        results['by_type'][config_type][country] = []
                    
                    results['by_type'][config_type][country].append(result['config'])
                    
                except Exception:
                    results['failed'] += 1
        
        self.cache_manager.cleanup()
        return results
    
    def save_results(self, classification_results: Dict[str, Any]) -> Dict[str, Any]:
        os.makedirs('configs/country', exist_ok=True)
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        all_countries_configs = []
        stats = {
            'total_countries': 0,
            'total_configs': 0,
            'by_country': {},
            'by_type': {},
            'unknown': len(classification_results['unknown']),
            'failed': classification_results['failed']
        }
        
        for country_code, country_data in classification_results['by_country'].items():
            stats['total_countries'] += 1
            country_dir = f"configs/country/{country_code}"
            os.makedirs(country_dir, exist_ok=True)
            
            all_configs = country_data['all']
            stats['total_configs'] += len(all_configs)
            stats['by_country'][country_code] = len(all_configs)
            
            all_countries_configs.extend(all_configs)
            
            all_file_content = f"# {country_code} - All Configurations\n"
            all_file_content += f"# Updated: {timestamp}\n"
            all_file_content += f"# Count: {len(all_configs)}\n\n"
            all_file_content += "\n".join(all_configs)
            
            with open(f"{country_dir}/all.txt", 'w', encoding='utf-8') as f:
                f.write(all_file_content)
            
            for config_type, type_configs in country_data['by_type'].items():
                if config_type not in stats['by_type']:
                    stats['by_type'][config_type] = 0
                stats['by_type'][config_type] += len(type_configs)
                
                type_file_content = f"# {country_code} - {config_type.upper()} Configurations\n"
                type_file_content += f"# Updated: {timestamp}\n"
                type_file_content += f"# Count: {len(type_configs)}\n\n"
                type_file_content += "\n".join(type_configs)
                
                with open(f"{country_dir}/{config_type}.txt", 'w', encoding='utf-8') as f:
                    f.write(type_file_content)
        
        if all_countries_configs:
            all_file_content = f"# All Country Configurations\n"
            all_file_content += f"# Updated: {timestamp}\n"
            all_file_content += f"# Total Count: {len(all_countries_configs)}\n"
            all_file_content += f"# Countries: {len(classification_results['by_country'])}\n\n"
            all_file_content += "\n".join(all_countries_configs)
            
            with open(f"configs/country/all.txt", 'w', encoding='utf-8') as f:
                f.write(all_file_content)
        
        if classification_results['unknown']:
            unknown_content = f"# Unknown Country Configurations\n"
            unknown_content += f"# Updated: {timestamp}\n"
            unknown_content += f"# Count: {len(classification_results['unknown'])}\n\n"
            unknown_content += "\n".join(classification_results['unknown'])
            
            with open(f"configs/country/unknown.txt", 'w', encoding='utf-8') as f:
                f.write(unknown_content)
        
        stats_file_content = f"# Classification Statistics\n"
        stats_file_content += f"# Updated: {timestamp}\n\n"
        stats_file_content += f"Total Countries: {stats['total_countries']}\n"
        stats_file_content += f"Total Configs: {stats['total_configs']}\n"
        stats_file_content += f"Unknown Configs: {stats['unknown']}\n"
        stats_file_content += f"Failed Configs: {stats['failed']}\n\n"
        
        stats_file_content += "By Country:\n"
        for country, count in sorted(stats['by_country'].items(), key=lambda x: x[1], reverse=True):
            stats_file_content += f"{country}: {count}\n"
        
        stats_file_content += "\nBy Type:\n"
        for config_type, count in sorted(stats['by_type'].items(), key=lambda x: x[1], reverse=True):
            stats_file_content += f"{config_type}: {count}\n"
        
        with open(f"configs/country/stats.txt", 'w', encoding='utf-8') as f:
            f.write(stats_file_content)
        
        return stats
    
    def __del__(self):
        for reader in self.geoip_readers.values():
            try:
                reader.close()
            except:
                pass

def main():
    print("=" * 60)
    print("ARISTA COUNTRY CLASSIFIER ENHANCED")
    print("=" * 60)
    
    try:
        combined_file = "configs/combined/all.txt"
        if not os.path.exists(combined_file):
            print(f"فایل {combined_file} یافت نشد!")
            return
        
        configs = []
        with open(combined_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    configs.append(line)
        
        print(f"تعداد کانفیگ‌ها برای پردازش: {len(configs)}")
        
        max_workers = int(os.environ.get('MAX_WORKERS', 10))
        classifier = CountryClassifier(max_workers=max_workers)
        
        results = classifier.classify_configs(configs)
        stats = classifier.save_results(results)
        
        print(f"\n✅ پردازش کامل شد")
        print(f"تعداد کشورها: {stats['total_countries']}")
        print(f"تعداد کل کانفیگ‌ها: {stats['total_configs']}")
        print(f"کانفیگ‌های نامعلوم: {stats['unknown']}")
        print(f"کانفیگ‌های ناموفق: {stats['failed']}")
        
        print("\n📁 ساختار پوشه‌ها:")
        print("configs/country/")
        print("├── all.txt")
        print("├── unknown.txt")
        print("├── stats.txt")
        print("└── [کد کشور]/")
        print("    ├── all.txt")
        print("    ├── vmess.txt")
        print("    ├── vless.txt")
        print("    ├── trojan.txt")
        print("    └── ...")
        
        top_countries = sorted(stats['by_country'].items(), key=lambda x: x[1], reverse=True)[:5]
        print(f"\n🏆 برترین کشورها:")
        for country, count in top_countries:
            print(f"  {country}: {count} کانفیگ")
        
    except Exception as e:
        print(f"\n❌ خطا: {e}")

if __name__ == "__main__":
    main()

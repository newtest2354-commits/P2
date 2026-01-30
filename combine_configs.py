import os
import hashlib
from datetime import datetime

class ConfigCombiner:
    def __init__(self):
        self.categories = [
            'vmess', 'vless', 'trojan', 'ss',
            'hysteria2', 'hysteria', 'tuic', 
            'wireguard', 'other'
        ]
    
    def read_configs(self, filepath):
        if not os.path.exists(filepath):
            return []
        
        configs = []
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    configs.append(line)
        
        return configs
    
    def deduplicate(self, configs):
        unique_configs = []
        seen_hashes = set()
        
        for config in configs:
            config_hash = hashlib.md5(config.encode()).hexdigest()
            if config_hash not in seen_hashes:
                seen_hashes.add(config_hash)
                unique_configs.append(config)
        
        return unique_configs
    
    def combine(self):
        os.makedirs('configs/combined', exist_ok=True)
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        all_combined = []
        
        for category in self.categories:
            telegram_configs = self.read_configs(f'configs/telegram/{category}.txt')
            github_configs = self.read_configs(f'configs/github/{category}.txt')
            
            combined_configs = telegram_configs + github_configs
            unique_configs = self.deduplicate(combined_configs)
            
            if unique_configs:
                filename = f"configs/combined/{category}.txt"
                content = f"# Combined {category.upper()} Configurations\n"
                content += f"# Updated: {timestamp}\n"
                content += f"# Count: {len(unique_configs)}\n"
                content += f"# Sources: Telegram ({len(telegram_configs)}) + GitHub ({len(github_configs)})\n\n"
                content += "\n".join(unique_configs)
                
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(content)
                
                all_combined.extend(unique_configs)
        
        if all_combined:
            filename = "configs/combined/all.txt"
            content = f"# All Combined Configurations\n"
            content += f"# Updated: {timestamp}\n"
            content += f"# Total Count: {len(all_combined)}\n"
            content += "# Sources: Telegram + GitHub\n\n"
            content += "\n".join(all_combined)
            
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(content)
        
        all_telegram = self.read_configs('configs/telegram/all.txt')
        all_github = self.read_configs('configs/github/all.txt')
        
        total_telegram = len(all_telegram)
        total_github = len(all_github)
        total_combined = len(all_combined)
        
        print("=" * 60)
        print("CONFIG COMBINER")
        print("=" * 60)
        print(f"Telegram configs: {total_telegram}")
        print(f"GitHub configs: {total_github}")
        print(f"Combined unique configs: {total_combined}")
        print("\n📁 Files created in configs/combined/:")
        for category in self.categories:
            if os.path.exists(f'configs/combined/{category}.txt'):
                with open(f'configs/combined/{category}.txt', 'r', encoding='utf-8') as f:
                    lines = [line for line in f if line.strip() and not line.startswith('#')]
                print(f"  {category}.txt: {len(lines)} configs")
        print(f"  all.txt: {total_combined} configs")
        print("=" * 60)

def main():
    combiner = ConfigCombiner()
    combiner.combine()

if __name__ == "__main__":
    main()

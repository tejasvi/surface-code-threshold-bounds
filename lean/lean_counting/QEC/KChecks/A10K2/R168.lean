import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t672 = true := by
  decide +kernel

theorem tot672 : totK PA10K2 A10K2.t672 = [0, 304031809754, 1241136433247, 1866856551342, 1328068419627, 268544033111, 6782479114, 0, 0, 0] := by
  decide +kernel

theorem rows673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t673 = true := by
  decide +kernel

theorem tot673 : totK PA10K2 A10K2.t673 = [0, 459942519120, 1769957566081, 2037709639435, 613713090555, 25027633033, 0, 0, 0, 0] := by
  decide +kernel

theorem rows674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t674 = true := by
  decide +kernel

theorem tot674 : totK PA10K2 A10K2.t674 = [0, 0, 572871118119, 1951692439302, 1767038349748, 424445421866, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t675 = true := by
  decide +kernel

theorem tot675 : totK PA10K2 A10K2.t675 = [0, 414749067874, 1453506996110, 1740078691279, 1022608191700, 197515855872, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

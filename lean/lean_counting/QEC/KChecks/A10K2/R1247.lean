import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4988 = true := by
  decide +kernel

theorem tot4988 : totK PA10K2 A10K2.t4988 = [0, 0, 573550064300, 1967041214823, 1709636072844, 412269465388, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows4989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4989 = true := by
  decide +kernel

theorem tot4989 : totK PA10K2 A10K2.t4989 = [0, 455239522804, 1529770767906, 1756672429857, 865392499841, 157096734687, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows4990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4990 = true := by
  decide +kernel

theorem tot4990 : totK PA10K2 A10K2.t4990 = [0, 331332348085, 1629390144807, 2087666351641, 665272879456, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4991 = true := by
  decide +kernel

theorem tot4991 : totK PA10K2 A10K2.t4991 = [0, 95817992017, 814593601782, 2102968655552, 1395904032492, 207631459116, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

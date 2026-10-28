import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7676 = true := by
  decide +kernel

theorem tot7676 : totK PA10K2 A10K2.t7676 = [0, 0, 0, 544681030302, 1915026037395, 1899415193259, 456526687664, 12129354050, 0, 0] := by
  decide +kernel

theorem rows7677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7677 = true := by
  decide +kernel

theorem tot7677 : totK PA10K2 A10K2.t7677 = [0, 0, 0, 0, 640963729270, 2032573535102, 1717508421140, 410103597148, 25734533292, 0] := by
  decide +kernel

theorem rows7678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7678 = true := by
  decide +kernel

theorem tot7678 : totK PA10K2 A10K2.t7678 = [0, 0, 0, 253882307211, 1117581745934, 1855575635517, 1184802773422, 200701373940, 6034215561, 0] := by
  decide +kernel

theorem rows7679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7679 = true := by
  decide +kernel

theorem tot7679 : totK PA10K2 A10K2.t7679 = [0, 0, 0, 428127261932, 1743826922642, 1929784357326, 544070238017, 32877822373, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7856 = true := by
  decide +kernel

theorem tot7856 : totK PA10K2 A10K2.t7856 = [0, 186042925296, 1177123845367, 2162378208590, 1289481203635, 210066345718, 15167097304, 0, 0, 0] := by
  decide +kernel

theorem rows7857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7857 = true := by
  decide +kernel

theorem tot7857 : totK PA10K2 A10K2.t7857 = [0, 139103737231, 812269539060, 1846824131056, 1598003113353, 394715158238, 16580095196, 0, 0, 0] := by
  decide +kernel

theorem rows7858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7858 = true := by
  decide +kernel

theorem tot7858 : totK PA10K2 A10K2.t7858 = [0, 501735697484, 1845000194178, 2026180477102, 623484838288, 44263552635, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7859 = true := by
  decide +kernel

theorem tot7859 : totK PA10K2 A10K2.t7859 = [0, 227811217789, 1250716107368, 2167339020033, 1210673342415, 145806919455, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

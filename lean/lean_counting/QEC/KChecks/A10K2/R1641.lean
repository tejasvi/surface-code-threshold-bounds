import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6564 = true := by
  decide +kernel

theorem tot6564 : totK PA10K2 A10K2.t6564 = [0, 0, 507212696927, 1733388764314, 1835745383800, 623993667251, 55539373477, 0, 0, 0] := by
  decide +kernel

theorem rows6565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6565 = true := by
  decide +kernel

theorem tot6565 : totK PA10K2 A10K2.t6565 = [0, 0, 234274142930, 1444512413918, 2152927291929, 807967863081, 51626803747, 0, 0, 0] := by
  decide +kernel

theorem rows6566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6566 = true := by
  decide +kernel

theorem tot6566 : totK PA10K2 A10K2.t6566 = [0, 0, 296670718154, 1231753555511, 1869315804978, 1103967236117, 188127585322, 6121173289, 0, 0] := by
  decide +kernel

theorem rows6567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6567 = true := by
  decide +kernel

theorem tot6567 : totK PA10K2 A10K2.t6567 = [0, 247698060303, 899733108572, 1557602279124, 1673978747488, 623044150083, 41230322852, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

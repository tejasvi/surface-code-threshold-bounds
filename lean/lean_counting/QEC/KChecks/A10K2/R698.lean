import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2792 = true := by
  decide +kernel

theorem tot2792 : totK PA10K2 A10K2.t2792 = [0, 143300517916, 1043218189725, 2098036791004, 1347436917851, 266890469517, 20070762815, 0, 0, 0] := by
  decide +kernel

theorem rows2793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2793 = true := by
  decide +kernel

theorem tot2793 : totK PA10K2 A10K2.t2793 = [0, 113566876963, 809226004630, 1926025446316, 1539158459960, 318255427086, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows2794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2794 = true := by
  decide +kernel

theorem tot2794 : totK PA10K2 A10K2.t2794 = [0, 446913455049, 1791969174814, 1989884486913, 569999793003, 32066831123, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2795 = true := by
  decide +kernel

theorem tot2795 : totK PA10K2 A10K2.t2795 = [0, 223715080400, 1045683348591, 1946804057505, 1247236594761, 187925687124, 5705019915, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

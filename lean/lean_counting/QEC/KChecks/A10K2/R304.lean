import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1216 = true := by
  decide +kernel

theorem tot1216 : totK PA10K2 A10K2.t1216 = [0, 0, 289205405109, 1518786560596, 2286175568103, 952271394764, 66933455818, 0, 0, 0] := by
  decide +kernel

theorem rows1217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1217 = true := by
  decide +kernel

theorem tot1217 : totK PA10K2 A10K2.t1217 = [0, 0, 375642859564, 1536498079984, 2048005055146, 927860918036, 101890577239, 0, 0, 0] := by
  decide +kernel

theorem rows1218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1218 = true := by
  decide +kernel

theorem tot1218 : totK PA10K2 A10K2.t1218 = [0, 0, 459692373802, 1822304364088, 2069217691670, 592592285584, 21394074235, 0, 0, 0] := by
  decide +kernel

theorem rows1219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1219 = true := by
  decide +kernel

theorem tot1219 : totK PA10K2 A10K2.t1219 = [0, 0, 0, 549797582815, 2010331756339, 2017136682355, 423197048216, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

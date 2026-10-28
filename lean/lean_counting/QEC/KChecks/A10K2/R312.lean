import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1248 = true := by
  decide +kernel

theorem tot1248 : totK PA10K2 A10K2.t1248 = [0, 272911534596, 1199726802492, 1874895774532, 1156411994512, 201926775963, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1249 = true := by
  decide +kernel

theorem tot1249 : totK PA10K2 A10K2.t1249 = [0, 549055494491, 1822488360232, 1694055495653, 482091525836, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1250 = true := by
  decide +kernel

theorem tot1250 : totK PA10K2 A10K2.t1250 = [0, 0, 935619123809, 2352598595187, 1224879328134, 113943173993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1251 = true := by
  decide +kernel

theorem tot1251 : totK PA10K2 A10K2.t1251 = [0, 0, 513193454314, 1839173545339, 1855812491066, 515690068205, 31987755669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

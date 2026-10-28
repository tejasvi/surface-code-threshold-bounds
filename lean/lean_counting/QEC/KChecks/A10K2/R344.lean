import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1376 = true := by
  decide +kernel

theorem tot1376 : totK PA10K2 A10K2.t1376 = [0, 0, 182725438514, 1326995713638, 2159135571573, 868424694577, 51918739330, 0, 0, 0] := by
  decide +kernel

theorem rows1377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1377 = true := by
  decide +kernel

theorem tot1377 : totK PA10K2 A10K2.t1377 = [0, 0, 0, 563951168813, 1957848087197, 1708069861350, 403654290131, 26601763172, 0, 0] := by
  decide +kernel

theorem rows1378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1378 = true := by
  decide +kernel

theorem tot1378 : totK PA10K2 A10K2.t1378 = [0, 0, 0, 488832805794, 1844953119998, 1998285524887, 483427408440, 18535904725, 0, 0] := by
  decide +kernel

theorem rows1379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1379 = true := by
  decide +kernel

theorem tot1379 : totK PA10K2 A10K2.t1379 = [0, 0, 0, 529843997034, 1908584837430, 1758136811489, 334094670424, 11881401544, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

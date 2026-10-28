import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1188 = true := by
  decide +kernel

theorem tot1188 : totK PA10K2 A10K2.t1188 = [0, 0, 0, 460095220005, 1903460940933, 1815264614489, 420382502985, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1189 = true := by
  decide +kernel

theorem tot1189 : totK PA10K2 A10K2.t1189 = [0, 0, 348431717547, 1500331274506, 1971869683212, 905544950915, 149519228999, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1190 = true := by
  decide +kernel

theorem tot1190 : totK PA10K2 A10K2.t1190 = [0, 0, 372942611595, 1615452203772, 1954860343365, 569249178175, 32768226799, 0, 0, 0] := by
  decide +kernel

theorem rows1191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1191 = true := by
  decide +kernel

theorem tot1191 : totK PA10K2 A10K2.t1191 = [0, 0, 201977367998, 998762780330, 1915229671566, 1209282809383, 179289924005, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

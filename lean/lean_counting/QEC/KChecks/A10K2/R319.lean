import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1276 = true := by
  decide +kernel

theorem tot1276 : totK PA10K2 A10K2.t1276 = [0, 0, 0, 466540110177, 1834705538006, 1815488071280, 470905451996, 31193230065, 0, 0] := by
  decide +kernel

theorem rows1277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1277 = true := by
  decide +kernel

theorem tot1277 : totK PA10K2 A10K2.t1277 = [0, 0, 0, 701541483763, 2171678130396, 1587914829485, 249568538943, 6354603908, 0, 0] := by
  decide +kernel

theorem rows1278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1278 = true := by
  decide +kernel

theorem tot1278 : totK PA10K2 A10K2.t1278 = [0, 0, 0, 607413524314, 1928034338730, 1617513965628, 378221108289, 25589850627, 0, 0] := by
  decide +kernel

theorem rows1279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1279 = true := by
  decide +kernel

theorem tot1279 : totK PA10K2 A10K2.t1279 = [0, 0, 0, 536452422018, 1929145664663, 1737965713882, 362883251975, 11323844185, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1252 = true := by
  decide +kernel

theorem tot1252 : totK PA10K2 A10K2.t1252 = [0, 0, 539457515608, 1914214361001, 1913483323046, 454654159179, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows1253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1253 = true := by
  decide +kernel

theorem tot1253 : totK PA10K2 A10K2.t1253 = [0, 0, 448025160474, 1791334948209, 1935820397120, 514335018940, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows1254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1254 = true := by
  decide +kernel

theorem tot1254 : totK PA10K2 A10K2.t1254 = [0, 0, 455766767026, 1744533658869, 1827483901126, 488319343857, 44363554315, 0, 0, 0] := by
  decide +kernel

theorem rows1255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1255 = true := by
  decide +kernel

theorem tot1255 : totK PA10K2 A10K2.t1255 = [0, 0, 306467343696, 1513577090017, 2064111356001, 704045062474, 52519180279, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

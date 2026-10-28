import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t356 = true := by
  decide +kernel

theorem tot356 : totK PD2M8K2 D2M8K2.t356 = [175884522944, 390238392481, 241108893424, 96140793262, 6679176959, 0, 0, 0] := by
  decide +kernel

theorem rows357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t357 = true := by
  decide +kernel

theorem tot357 : totK PD2M8K2 D2M8K2.t357 = [181097966188, 434070208516, 274336286926, 29662355562, 0, 0, 0, 0] := by
  decide +kernel

theorem rows358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t358 = true := by
  decide +kernel

theorem tot358 : totK PD2M8K2 D2M8K2.t358 = [88921332855, 415038605891, 359810494797, 39252534945, 0, 0, 0, 0] := by
  decide +kernel

theorem rows359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t359 = true := by
  decide +kernel

theorem tot359 : totK PD2M8K2 D2M8K2.t359 = [0, 219752573178, 491529757479, 178230675797, 9587713104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

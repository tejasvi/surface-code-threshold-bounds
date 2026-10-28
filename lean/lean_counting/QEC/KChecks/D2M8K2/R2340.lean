import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9360 = true := by
  decide +kernel

theorem tot9360 : totK PD2M8K2 D2M8K2.t9360 = [0, 157426159975, 390830877096, 280093829409, 77551637769, 3455941720, 0, 0] := by
  decide +kernel

theorem rows9361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9361 = true := by
  decide +kernel

theorem tot9361 : totK PD2M8K2 D2M8K2.t9361 = [0, 177606368184, 431245755105, 277199104225, 30587065052, 0, 0, 0] := by
  decide +kernel

theorem rows9362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9362 = true := by
  decide +kernel

theorem tot9362 : totK PD2M8K2 D2M8K2.t9362 = [0, 80559306243, 420498077840, 366108854986, 40899430745, 0, 0, 0] := by
  decide +kernel

theorem rows9363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9363 = true := by
  decide +kernel

theorem tot9363 : totK PD2M8K2 D2M8K2.t9363 = [0, 0, 220128510362, 489682982138, 167027411591, 9473607896, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

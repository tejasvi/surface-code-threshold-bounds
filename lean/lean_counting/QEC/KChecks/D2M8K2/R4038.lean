import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16152 = true := by
  decide +kernel

theorem tot16152 : totK PD2M8K2 D2M8K2.t16152 = [0, 0, 177430329409, 453175538978, 268873876680, 28722304528, 0, 0] := by
  decide +kernel

theorem rows16153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16153 = true := by
  decide +kernel

theorem tot16153 : totK PD2M8K2 D2M8K2.t16153 = [0, 0, 166387527578, 490605874355, 241324445146, 7894040542, 0, 0] := by
  decide +kernel

theorem rows16154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16154 = true := by
  decide +kernel

theorem tot16154 : totK PD2M8K2 D2M8K2.t16154 = [0, 0, 174665947218, 464740701278, 243667970655, 20949581993, 0, 0] := by
  decide +kernel

theorem rows16155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16155 = true := by
  decide +kernel

theorem tot16155 : totK PD2M8K2 D2M8K2.t16155 = [0, 0, 192287396963, 457547026453, 224538918936, 15111117465, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

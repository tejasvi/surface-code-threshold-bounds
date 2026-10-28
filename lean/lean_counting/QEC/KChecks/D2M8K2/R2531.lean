import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10124 = true := by
  decide +kernel

theorem tot10124 : totK PD2M8K2 D2M8K2.t10124 = [0, 170343765743, 396283166744, 211498189896, 88028112012, 12073505261, 0, 0] := by
  decide +kernel

theorem rows10125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10125 = true := by
  decide +kernel

theorem tot10125 : totK PD2M8K2 D2M8K2.t10125 = [0, 153258232679, 459350729718, 267357568858, 18645335646, 0, 0, 0] := by
  decide +kernel

theorem rows10126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10126 = true := by
  decide +kernel

theorem tot10126 : totK PD2M8K2 D2M8K2.t10126 = [0, 0, 279318952781, 508581728177, 104278211975, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10127 = true := by
  decide +kernel

theorem tot10127 : totK PD2M8K2 D2M8K2.t10127 = [0, 179148547845, 444170920268, 267876532388, 28666649823, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

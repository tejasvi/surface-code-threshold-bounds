import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13828 = true := by
  decide +kernel

theorem tot13828 : totK PD2M8K2 D2M8K2.t13828 = [0, 223336800763, 485286935822, 168132963065, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows13829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13829 = true := by
  decide +kernel

theorem tot13829 : totK PD2M8K2 D2M8K2.t13829 = [151660303848, 409911098509, 287593281313, 58504800061, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows13830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13830 = true := by
  decide +kernel

theorem tot13830 : totK PD2M8K2 D2M8K2.t13830 = [141750973803, 431256743466, 301923602081, 27190993221, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13831 = true := by
  decide +kernel

theorem tot13831 : totK PD2M8K2 D2M8K2.t13831 = [85070550086, 361214801626, 369650295350, 68704411610, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

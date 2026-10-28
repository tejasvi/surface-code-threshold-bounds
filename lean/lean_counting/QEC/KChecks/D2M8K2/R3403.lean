import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13612 = true := by
  decide +kernel

theorem tot13612 : totK PD2M8K2 D2M8K2.t13612 = [0, 220597001791, 493654760911, 164514254294, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows13613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13613 = true := by
  decide +kernel

theorem tot13613 : totK PD2M8K2 D2M8K2.t13613 = [85190975889, 303160222950, 367742440681, 117602093615, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows13614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13614 = true := by
  decide +kernel

theorem tot13614 : totK PD2M8K2 D2M8K2.t13614 = [160215621709, 453572217065, 271174659244, 25283261709, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13615 = true := by
  decide +kernel

theorem tot13615 : totK PD2M8K2 D2M8K2.t13615 = [154963882537, 453973198035, 269167827259, 18722719276, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

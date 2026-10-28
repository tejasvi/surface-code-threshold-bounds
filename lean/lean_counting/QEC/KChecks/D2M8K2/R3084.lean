import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12336 = true := by
  decide +kernel

theorem tot12336 : totK PD2M8K2 D2M8K2.t12336 = [0, 185961349168, 481294720831, 218511731735, 14633607569, 0, 0, 0] := by
  decide +kernel

theorem rows12337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12337 = true := by
  decide +kernel

theorem tot12337 : totK PD2M8K2 D2M8K2.t12337 = [0, 165053295238, 473148787812, 239432031925, 10875644221, 0, 0, 0] := by
  decide +kernel

theorem rows12338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12338 = true := by
  decide +kernel

theorem tot12338 : totK PD2M8K2 D2M8K2.t12338 = [0, 181147864850, 460785589829, 248927495910, 18246066036, 0, 0, 0] := by
  decide +kernel

theorem rows12339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12339 = true := by
  decide +kernel

theorem tot12339 : totK PD2M8K2 D2M8K2.t12339 = [0, 206370711700, 481604719716, 197176263027, 7651299259, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

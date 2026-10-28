import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11800 = true := by
  decide +kernel

theorem tot11800 : totK PD2M8K2 D2M8K2.t11800 = [0, 0, 198855528403, 483727772779, 193479682481, 9840992866, 0, 0] := by
  decide +kernel

theorem rows11801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11801 = true := by
  decide +kernel

theorem tot11801 : totK PD2M8K2 D2M8K2.t11801 = [0, 0, 186285050665, 474491941905, 173558285905, 6050748506, 0, 0] := by
  decide +kernel

theorem rows11802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11802 = true := by
  decide +kernel

theorem tot11802 : totK PD2M8K2 D2M8K2.t11802 = [0, 0, 0, 291844925272, 453809797899, 84886035434, 1206465782, 0] := by
  decide +kernel

theorem rows11803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11803 = true := by
  decide +kernel

theorem tot11803 : totK PD2M8K2 D2M8K2.t11803 = [0, 0, 118261042653, 411560055638, 322121357725, 33928674619, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

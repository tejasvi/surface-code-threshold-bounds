import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13252 = true := by
  decide +kernel

theorem tot13252 : totK PD2M8K2 D2M8K2.t13252 = [0, 157096909914, 384945098128, 264495301776, 98401078839, 6804944647, 0, 0] := by
  decide +kernel

theorem rows13253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13253 = true := by
  decide +kernel

theorem tot13253 : totK PD2M8K2 D2M8K2.t13253 = [0, 177769216434, 471807049807, 235716967516, 13956247425, 0, 0, 0] := by
  decide +kernel

theorem rows13254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13254 = true := by
  decide +kernel

theorem tot13254 : totK PD2M8K2 D2M8K2.t13254 = [0, 78908693579, 337903385036, 395059369587, 81571832591, 1163840124, 0, 0] := by
  decide +kernel

theorem rows13255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13255 = true := by
  decide +kernel

theorem tot13255 : totK PD2M8K2 D2M8K2.t13255 = [0, 0, 194637361039, 485153846382, 183788810675, 10369431706, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

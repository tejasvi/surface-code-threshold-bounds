import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12204 = true := by
  decide +kernel

theorem tot12204 : totK PD2M8K2 D2M8K2.t12204 = [0, 201181613362, 508534135601, 196407064083, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows12205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12205 = true := by
  decide +kernel

theorem tot12205 : totK PD2M8K2 D2M8K2.t12205 = [157096909914, 386252524308, 262681620390, 98401078839, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows12206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12206 = true := by
  decide +kernel

theorem tot12206 : totK PD2M8K2 D2M8K2.t12206 = [177769216434, 471807049807, 232801370948, 15359369050, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12207 = true := by
  decide +kernel

theorem tot12207 : totK PD2M8K2 D2M8K2.t12207 = [78908693579, 335201313779, 393114649613, 88288100138, 1163840124, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

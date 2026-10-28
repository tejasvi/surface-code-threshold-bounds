import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11212 = true := by
  decide +kernel

theorem tot11212 : totK PD2M8K2 D2M8K2.t11212 = [0, 0, 178314817228, 480988392254, 205177339650, 8537527025, 0, 0] := by
  decide +kernel

theorem rows11213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11213 = true := by
  decide +kernel

theorem tot11213 : totK PD2M8K2 D2M8K2.t11213 = [183285179032, 397829498317, 209490663391, 58327924473, 67331261689, 12110122745, 0, 0] := by
  decide +kernel

theorem rows11214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11214 = true := by
  decide +kernel

theorem tot11214 : totK PD2M8K2 D2M8K2.t11214 = [177001541420, 468674307928, 252034763855, 16494788818, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11215 = true := by
  decide +kernel

theorem tot11215 : totK PD2M8K2 D2M8K2.t11215 = [89132330960, 378451713907, 365304637035, 82139977123, 10444649207, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

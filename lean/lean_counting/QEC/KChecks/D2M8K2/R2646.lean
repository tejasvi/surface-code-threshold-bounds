import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10584 = true := by
  decide +kernel

theorem tot10584 : totK PD2M8K2 D2M8K2.t10584 = [0, 0, 84580619592, 416038448259, 356334428085, 23872077298, 0, 0] := by
  decide +kernel

theorem rows10585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10585 = true := by
  decide +kernel

theorem tot10585 : totK PD2M8K2 D2M8K2.t10585 = [0, 0, 164800768176, 453151350422, 269830052999, 29185162439, 0, 0] := by
  decide +kernel

theorem rows10586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10586 = true := by
  decide +kernel

theorem tot10586 : totK PD2M8K2 D2M8K2.t10586 = [0, 0, 163967401476, 470527526820, 257532378113, 14314032282, 0, 0] := by
  decide +kernel

theorem rows10587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10587 = true := by
  decide +kernel

theorem tot10587 : totK PD2M8K2 D2M8K2.t10587 = [0, 0, 197277137464, 482904220909, 207258291210, 11147461985, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

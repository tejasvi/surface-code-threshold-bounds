import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5580 = true := by
  decide +kernel

theorem tot5580 : totK PD2M8K2 D2M8K2.t5580 = [0, 218952947009, 500151839239, 172974957052, 7233348802, 0, 0, 0] := by
  decide +kernel

theorem rows5581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5581 = true := by
  decide +kernel

theorem tot5581 : totK PD2M8K2 D2M8K2.t5581 = [84865244063, 285928947610, 378136187755, 124054884770, 6017336459, 0, 0, 0] := by
  decide +kernel

theorem rows5582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5582 = true := by
  decide +kernel

theorem tot5582 : totK PD2M8K2 D2M8K2.t5582 = [135732198731, 445784131064, 281802272424, 25839749978, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5583 = true := by
  decide +kernel

theorem tot5583 : totK PD2M8K2 D2M8K2.t5583 = [177492465105, 470261557082, 236098350724, 13998332970, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6528 = true := by
  decide +kernel

theorem tot6528 : totK PD2M8K2 D2M8K2.t6528 = [0, 277574344555, 504732566336, 121116887532, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows6529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6529 = true := by
  decide +kernel

theorem tot6529 : totK PD2M8K2 D2M8K2.t6529 = [0, 190665860826, 466963770370, 213754192273, 16927693697, 0, 0, 0] := by
  decide +kernel

theorem rows6530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6530 = true := by
  decide +kernel

theorem tot6530 : totK PD2M8K2 D2M8K2.t6530 = [0, 170119050899, 469888552260, 225960196373, 11023652771, 0, 0, 0] := by
  decide +kernel

theorem rows6531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6531 = true := by
  decide +kernel

theorem tot6531 : totK PD2M8K2 D2M8K2.t6531 = [0, 163167778945, 463339941700, 235447308196, 12659244494, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

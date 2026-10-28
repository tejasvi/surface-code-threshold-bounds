import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5940 = true := by
  decide +kernel

theorem tot5940 : totK PD2M8K2 D2M8K2.t5940 = [0, 172914388706, 438158657444, 273236439497, 28520273273, 0, 0, 0] := by
  decide +kernel

theorem rows5941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5941 = true := by
  decide +kernel

theorem tot5941 : totK PD2M8K2 D2M8K2.t5941 = [0, 215228688549, 485331212566, 204752574261, 7950525988, 0, 0, 0] := by
  decide +kernel

theorem rows5942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5942 = true := by
  decide +kernel

theorem tot5942 : totK PD2M8K2 D2M8K2.t5942 = [0, 186194627238, 481932562441, 229982841119, 14800140588, 0, 0, 0] := by
  decide +kernel

theorem rows5943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5943 = true := by
  decide +kernel

theorem tot5943 : totK PD2M8K2 D2M8K2.t5943 = [0, 159565026647, 430442070419, 279169550095, 28952850019, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10932 = true := by
  decide +kernel

theorem tot10932 : totK PD2M8K2 D2M8K2.t10932 = [0, 0, 84265373804, 309574021591, 373014088040, 96581373802, 3804183361, 0] := by
  decide +kernel

theorem rows10933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10933 = true := by
  decide +kernel

theorem tot10933 : totK PD2M8K2 D2M8K2.t10933 = [0, 0, 179755076763, 462935611960, 251004475470, 20859766089, 0, 0] := by
  decide +kernel

theorem rows10934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10934 = true := by
  decide +kernel

theorem tot10934 : totK PD2M8K2 D2M8K2.t10934 = [0, 0, 156878551535, 465192829088, 261288710509, 16000064993, 0, 0] := by
  decide +kernel

theorem rows10935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10935 = true := by
  decide +kernel

theorem tot10935 : totK PD2M8K2 D2M8K2.t10935 = [0, 0, 0, 277305880733, 493600358195, 102569112351, 1107157161, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15472 = true := by
  decide +kernel

theorem tot15472 : totK PD2M8K2 D2M8K2.t15472 = [0, 0, 193148086518, 486867109098, 213527158599, 6534384359, 0, 0] := by
  decide +kernel

theorem rows15473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15473 = true := by
  decide +kernel

theorem tot15473 : totK PD2M8K2 D2M8K2.t15473 = [0, 151336384243, 368872029289, 272631319407, 106889806825, 6804944647, 0, 0] := by
  decide +kernel

theorem rows15474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15474 = true := by
  decide +kernel

theorem tot15474 : totK PD2M8K2 D2M8K2.t15474 = [0, 166128269513, 436478933051, 281302422338, 30303715720, 0, 0, 0] := by
  decide +kernel

theorem rows15475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15475 = true := by
  decide +kernel

theorem tot15475 : totK PD2M8K2 D2M8K2.t15475 = [0, 93285103190, 391336483319, 354218377515, 56670969069, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

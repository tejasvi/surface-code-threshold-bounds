import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12644 = true := by
  decide +kernel

theorem tot12644 : totK PD2M8K2 D2M8K2.t12644 = [0, 0, 116791540598, 428320930333, 321935279772, 27227222165, 0, 0] := by
  decide +kernel

theorem rows12645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12645 = true := by
  decide +kernel

theorem tot12645 : totK PD2M8K2 D2M8K2.t12645 = [0, 0, 0, 319080639458, 473219693687, 95317666765, 1268739303, 0] := by
  decide +kernel

theorem rows12646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12646 = true := by
  decide +kernel

theorem tot12646 : totK PD2M8K2 D2M8K2.t12646 = [0, 0, 0, 205553743986, 482763901486, 184906047627, 9610913563, 0] := by
  decide +kernel

theorem rows12647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12647 = true := by
  decide +kernel

theorem tot12647 : totK PD2M8K2 D2M8K2.t12647 = [0, 0, 0, 201591872467, 465444378978, 185601732165, 12206147664, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

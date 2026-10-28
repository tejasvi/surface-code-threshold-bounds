import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3828 = true := by
  decide +kernel

theorem tot3828 : totK PD2M8K2 D2M8K2.t3828 = [188258557265, 483538096418, 210652217655, 9716706633, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3829 = true := by
  decide +kernel

theorem tot3829 : totK PD2M8K2 D2M8K2.t3829 = [139815167308, 442692174464, 283602401135, 23218540302, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3830 = true := by
  decide +kernel

theorem tot3830 : totK PD2M8K2 D2M8K2.t3830 = [0, 269532176075, 503385235210, 109136949271, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3831 = true := by
  decide +kernel

theorem tot3831 : totK PD2M8K2 D2M8K2.t3831 = [122528881355, 389271048324, 362814789943, 50219395744, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

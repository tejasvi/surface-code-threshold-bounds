import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15192 = true := by
  decide +kernel

theorem tot15192 : totK PD2M8K2 D2M8K2.t15192 = [0, 207642756040, 463179670410, 210663895851, 12526078277, 0, 0, 0] := by
  decide +kernel

theorem rows15193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15193 = true := by
  decide +kernel

theorem tot15193 : totK PD2M8K2 D2M8K2.t15193 = [0, 19497166104, 311550202317, 465770629682, 99975073281, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15194 = true := by
  decide +kernel

theorem tot15194 : totK PD2M8K2 D2M8K2.t15194 = [0, 90376631047, 366094963640, 413777305071, 53122048194, 0, 0, 0] := by
  decide +kernel

theorem rows15195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15195 = true := by
  decide +kernel

theorem tot15195 : totK PD2M8K2 D2M8K2.t15195 = [0, 168035750174, 453812100050, 274926942717, 26384395661, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

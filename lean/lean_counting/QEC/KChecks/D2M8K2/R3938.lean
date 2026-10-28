import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15752 = true := by
  decide +kernel

theorem tot15752 : totK PD2M8K2 D2M8K2.t15752 = [0, 0, 87533885883, 384060792243, 396780980452, 29166905410, 0, 0] := by
  decide +kernel

theorem rows15753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15753 = true := by
  decide +kernel

theorem tot15753 : totK PD2M8K2 D2M8K2.t15753 = [0, 0, 178380338125, 453796640947, 264934254286, 30465585733, 0, 0] := by
  decide +kernel

theorem rows15754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15754 = true := by
  decide +kernel

theorem tot15754 : totK PD2M8K2 D2M8K2.t15754 = [0, 0, 226378681990, 508286651850, 166490074687, 4171150218, 0, 0] := by
  decide +kernel

theorem rows15755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15755 = true := by
  decide +kernel

theorem tot15755 : totK PD2M8K2 D2M8K2.t15755 = [0, 0, 173552327458, 450324571593, 270281168541, 21022135231, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

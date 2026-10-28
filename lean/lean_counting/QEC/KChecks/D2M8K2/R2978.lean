import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11912 = true := by
  decide +kernel

theorem tot11912 : totK PD2M8K2 D2M8K2.t11912 = [90526578066, 359477759233, 367212020011, 80931794774, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows11913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11913 = true := by
  decide +kernel

theorem tot11913 : totK PD2M8K2 D2M8K2.t11913 = [0, 229488727111, 491779954639, 166611446928, 6321703496, 0, 0, 0] := by
  decide +kernel

theorem rows11914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11914 = true := by
  decide +kernel

theorem tot11914 : totK PD2M8K2 D2M8K2.t11914 = [0, 149336449675, 434489246637, 295389645857, 32029612991, 0, 0, 0] := by
  decide +kernel

theorem rows11915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11915 = true := by
  decide +kernel

theorem tot11915 : totK PD2M8K2 D2M8K2.t11915 = [0, 197910813076, 470023935671, 230846493673, 15003876942, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

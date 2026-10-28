import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2908 = true := by
  decide +kernel

theorem tot2908 : totK PD2M8K2 D2M8K2.t2908 = [0, 223891862335, 492969984289, 160456933896, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows2909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2909 = true := by
  decide +kernel

theorem tot2909 : totK PD2M8K2 D2M8K2.t2909 = [66418003249, 284883897355, 396025127662, 123793507071, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows2910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2910 = true := by
  decide +kernel

theorem tot2910 : totK PD2M8K2 D2M8K2.t2910 = [173151697332, 456416651412, 270133534919, 27948873865, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2911 = true := by
  decide +kernel

theorem tot2911 : totK PD2M8K2 D2M8K2.t2911 = [87646833503, 369702389001, 358482539658, 72041371272, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

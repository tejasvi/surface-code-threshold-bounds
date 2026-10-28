import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14848 = true := by
  decide +kernel

theorem tot14848 : totK PD2M8K2 D2M8K2.t14848 = [0, 281063233010, 510477312711, 111582755104, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14849 = true := by
  decide +kernel

theorem tot14849 : totK PD2M8K2 D2M8K2.t14849 = [0, 206406778772, 465487533783, 191184754910, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows14850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14850 = true := by
  decide +kernel

theorem tot14850 : totK PD2M8K2 D2M8K2.t14850 = [163872679784, 440943902410, 273421574803, 30951526035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14851 = true := by
  decide +kernel

theorem tot14851 : totK PD2M8K2 D2M8K2.t14851 = [160245867212, 450613102356, 264484016280, 22823938281, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

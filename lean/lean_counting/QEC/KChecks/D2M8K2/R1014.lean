import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4056 = true := by
  decide +kernel

theorem tot4056 : totK PD2M8K2 D2M8K2.t4056 = [0, 0, 0, 224118494236, 506525962396, 152200968911, 2484078857, 0] := by
  decide +kernel

theorem rows4057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4057 = true := by
  decide +kernel

theorem tot4057 : totK PD2M8K2 D2M8K2.t4057 = [0, 159221153091, 377112284693, 152740219573, 100328267936, 89739485913, 6818291842, 0] := by
  decide +kernel

theorem rows4058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4058 = true := by
  decide +kernel

theorem tot4058 : totK PD2M8K2 D2M8K2.t4058 = [0, 163632999621, 448471852803, 258199775585, 18482339656, 0, 0, 0] := by
  decide +kernel

theorem rows4059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4059 = true := by
  decide +kernel

theorem tot4059 : totK PD2M8K2 D2M8K2.t4059 = [0, 19982922235, 333243470515, 496682583893, 62131267243, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

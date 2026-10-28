import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11904 = true := by
  decide +kernel

theorem tot11904 : totK PD2M8K2 D2M8K2.t11904 = [101166807539, 403684771130, 335867105296, 44407836052, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows11905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11905 = true := by
  decide +kernel

theorem tot11905 : totK PD2M8K2 D2M8K2.t11905 = [0, 229815207246, 487793566148, 172870523621, 8464368736, 0, 0, 0] := by
  decide +kernel

theorem rows11906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11906 = true := by
  decide +kernel

theorem tot11906 : totK PD2M8K2 D2M8K2.t11906 = [101180317635, 331750930823, 353744704418, 95377957949, 3575904516, 0, 0, 0] := by
  decide +kernel

theorem rows11907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11907 = true := by
  decide +kernel

theorem tot11907 : totK PD2M8K2 D2M8K2.t11907 = [170183578876, 444914552435, 274192415335, 30456879466, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

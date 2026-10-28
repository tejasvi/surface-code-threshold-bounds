import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12704 = true := by
  decide +kernel

theorem tot12704 : totK PD2M8K2 D2M8K2.t12704 = [0, 0, 37084170812, 278362760796, 455401701223, 123486656494, 3884009855, 0] := by
  decide +kernel

theorem rows12705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12705 = true := by
  decide +kernel

theorem tot12705 : totK PD2M8K2 D2M8K2.t12705 = [0, 0, 202667982650, 478657786741, 198262607242, 6607276259, 0, 0] := by
  decide +kernel

theorem rows12706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12706 = true := by
  decide +kernel

theorem tot12706 : totK PD2M8K2 D2M8K2.t12706 = [0, 0, 175585308140, 459934786729, 228329405293, 8760361787, 0, 0] := by
  decide +kernel

theorem rows12707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12707 = true := by
  decide +kernel

theorem tot12707 : totK PD2M8K2 D2M8K2.t12707 = [0, 0, 0, 290704480757, 476381538557, 101256838599, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

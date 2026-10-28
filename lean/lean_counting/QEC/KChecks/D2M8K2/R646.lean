import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2584 = true := by
  decide +kernel

theorem tot2584 : totK PD2M8K2 D2M8K2.t2584 = [0, 297207306471, 493493325405, 101885183513, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows2585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2585 = true := by
  decide +kernel

theorem tot2585 : totK PD2M8K2 D2M8K2.t2585 = [126560246313, 391633187978, 364576359299, 49933132682, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2586 = true := by
  decide +kernel

theorem tot2586 : totK PD2M8K2 D2M8K2.t2586 = [178685956779, 464931988489, 244307203956, 16434569015, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2587 = true := by
  decide +kernel

theorem tot2587 : totK PD2M8K2 D2M8K2.t2587 = [126108905853, 442079229620, 319137054377, 36195443089, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14784 = true := by
  decide +kernel

theorem tot14784 : totK PD2M8K2 D2M8K2.t14784 = [0, 176933040480, 490403315505, 241468681067, 8741128273, 0, 0, 0] := by
  decide +kernel

theorem rows14785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14785 = true := by
  decide +kernel

theorem tot14785 : totK PD2M8K2 D2M8K2.t14785 = [0, 0, 242032499292, 450706166086, 195448007243, 21385604922, 0, 0] := by
  decide +kernel

theorem rows14786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14786 = true := by
  decide +kernel

theorem tot14786 : totK PD2M8K2 D2M8K2.t14786 = [0, 0, 169450054762, 487325752573, 213004818770, 7658844075, 0, 0] := by
  decide +kernel

theorem rows14787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14787 = true := by
  decide +kernel

theorem tot14787 : totK PD2M8K2 D2M8K2.t14787 = [0, 117006550469, 326069231224, 309738410133, 131148743650, 7877424857, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

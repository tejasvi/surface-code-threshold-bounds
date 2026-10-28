import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows64 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t64 = true := by
  decide +kernel

theorem tot64 : totK PD2M8K2 D2M8K2.t64 = [0, 137494611656, 443961341501, 271734743027, 17483677410, 0, 0, 0] := by
  decide +kernel

theorem rows65 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t65 = true := by
  decide +kernel

theorem tot65 : totK PD2M8K2 D2M8K2.t65 = [0, 0, 298300113425, 472289418802, 78823463417, 1021600638, 0, 0] := by
  decide +kernel

theorem rows66 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t66 = true := by
  decide +kernel

theorem tot66 : totK PD2M8K2 D2M8K2.t66 = [0, 164436526882, 391106261383, 246255206604, 69127273834, 3552795014, 0, 0] := by
  decide +kernel

theorem rows67 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t67 = true := by
  decide +kernel

theorem tot67 : totK PD2M8K2 D2M8K2.t67 = [0, 156540335737, 447627579196, 277442767175, 19560755470, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

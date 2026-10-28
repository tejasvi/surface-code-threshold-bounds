import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t700 = true := by
  decide +kernel

theorem tot700 : totK PD2M8K2 D2M8K2.t700 = [132573296051, 361211351017, 306905625059, 76278022021, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t701 = true := by
  decide +kernel

theorem tot701 : totK PD2M8K2 D2M8K2.t701 = [163237021102, 443295647885, 274487574493, 29764034016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t702 = true := by
  decide +kernel

theorem tot702 : totK PD2M8K2 D2M8K2.t702 = [124209128497, 437779235099, 309953156128, 25043769601, 0, 0, 0, 0] := by
  decide +kernel

theorem rows703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t703 = true := by
  decide +kernel

theorem tot703 : totK PD2M8K2 D2M8K2.t703 = [0, 201812227623, 477878954686, 190057114513, 9668735432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

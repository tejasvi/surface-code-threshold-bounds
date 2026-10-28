import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t812 = true := by
  decide +kernel

theorem tot812 : totK PD2M8K2 D2M8K2.t812 = [0, 0, 200945647739, 450459372799, 222783086760, 19572653258, 0, 0] := by
  decide +kernel

theorem rows813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t813 = true := by
  decide +kernel

theorem tot813 : totK PD2M8K2 D2M8K2.t813 = [0, 0, 171065133245, 493836293143, 207933669458, 5430665091, 0, 0] := by
  decide +kernel

theorem rows814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t814 = true := by
  decide +kernel

theorem tot814 : totK PD2M8K2 D2M8K2.t814 = [0, 175642164599, 424169203978, 229833427395, 72289222901, 5147854625, 0, 0] := by
  decide +kernel

theorem rows815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t815 = true := by
  decide +kernel

theorem tot815 : totK PD2M8K2 D2M8K2.t815 = [0, 180879612968, 471992608536, 245793720632, 15479723709, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

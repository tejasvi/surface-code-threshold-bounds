import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7804 = true := by
  decide +kernel

theorem tot7804 : totK PD2M8K2 D2M8K2.t7804 = [0, 0, 165106982339, 471411400579, 229395560241, 12885670648, 0, 0] := by
  decide +kernel

theorem rows7805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7805 = true := by
  decide +kernel

theorem tot7805 : totK PD2M8K2 D2M8K2.t7805 = [0, 0, 213055381328, 468038378895, 190653900123, 9812437177, 0, 0] := by
  decide +kernel

theorem rows7806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7806 = true := by
  decide +kernel

theorem tot7806 : totK PD2M8K2 D2M8K2.t7806 = [0, 0, 171457578952, 494991360366, 213506364790, 6364565315, 0, 0] := by
  decide +kernel

theorem rows7807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7807 = true := by
  decide +kernel

theorem tot7807 : totK PD2M8K2 D2M8K2.t7807 = [0, 0, 206348402628, 466657112102, 198227288877, 9757737807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

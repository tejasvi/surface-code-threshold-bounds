import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13144 = true := by
  decide +kernel

theorem tot13144 : totK PD2M8K2 D2M8K2.t13144 = [0, 0, 195020700343, 483663749420, 215968349404, 11450238666, 0, 0] := by
  decide +kernel

theorem rows13145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13145 = true := by
  decide +kernel

theorem tot13145 : totK PD2M8K2 D2M8K2.t13145 = [0, 0, 180159297034, 438859659498, 271557239081, 26263358419, 0, 0] := by
  decide +kernel

theorem rows13146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13146 = true := by
  decide +kernel

theorem tot13146 : totK PD2M8K2 D2M8K2.t13146 = [0, 0, 87965710978, 409053648863, 342953595784, 37444870482, 0, 0] := by
  decide +kernel

theorem rows13147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13147 = true := by
  decide +kernel

theorem tot13147 : totK PD2M8K2 D2M8K2.t13147 = [0, 0, 0, 224993340619, 470606123424, 167019642727, 9633262574, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

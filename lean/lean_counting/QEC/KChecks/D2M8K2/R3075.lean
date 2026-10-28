import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12300 = true := by
  decide +kernel

theorem tot12300 : totK PD2M8K2 D2M8K2.t12300 = [0, 199571701307, 487983602512, 213458383916, 11311631362, 0, 0, 0] := by
  decide +kernel

theorem rows12301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12301 = true := by
  decide +kernel

theorem tot12301 : totK PD2M8K2 D2M8K2.t12301 = [0, 192211100017, 476804680237, 216000211635, 12481784551, 0, 0, 0] := by
  decide +kernel

theorem rows12302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12302 = true := by
  decide +kernel

theorem tot12302 : totK PD2M8K2 D2M8K2.t12302 = [0, 180092531185, 437017607533, 269146359051, 27200262724, 0, 0, 0] := by
  decide +kernel

theorem rows12303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12303 = true := by
  decide +kernel

theorem tot12303 : totK PD2M8K2 D2M8K2.t12303 = [0, 83196296163, 386688705165, 344474553260, 51902354130, 1171084559, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5512 = true := by
  decide +kernel

theorem tot5512 : totK PD2M8K2 D2M8K2.t5512 = [0, 200294418097, 468639286318, 190640085440, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows5513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5513 = true := by
  decide +kernel

theorem tot5513 : totK PD2M8K2 D2M8K2.t5513 = [139701926982, 435395892610, 297467285190, 29682100102, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5514 = true := by
  decide +kernel

theorem tot5514 : totK PD2M8K2 D2M8K2.t5514 = [188053214101, 450802370345, 225678932698, 16863123949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5515 = true := by
  decide +kernel

theorem tot5515 : totK PD2M8K2 D2M8K2.t5515 = [72181740977, 335008359672, 400572259831, 81598607859, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

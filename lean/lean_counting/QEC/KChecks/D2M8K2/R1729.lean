import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6916 = true := by
  decide +kernel

theorem tot6916 : totK PD2M8K2 D2M8K2.t6916 = [0, 177879713851, 458484100366, 245660418507, 14253691616, 0, 0, 0] := by
  decide +kernel

theorem rows6917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6917 = true := by
  decide +kernel

theorem tot6917 : totK PD2M8K2 D2M8K2.t6917 = [0, 0, 287260122598, 492273184766, 115348310051, 1268739303, 0, 0] := by
  decide +kernel

theorem rows6918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6918 = true := by
  decide +kernel

theorem tot6918 : totK PD2M8K2 D2M8K2.t6918 = [0, 0, 208950945737, 479017872326, 173509474016, 7309610657, 0, 0] := by
  decide +kernel

theorem rows6919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6919 = true := by
  decide +kernel

theorem tot6919 : totK PD2M8K2 D2M8K2.t6919 = [0, 0, 178586387761, 475429621524, 222463580470, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

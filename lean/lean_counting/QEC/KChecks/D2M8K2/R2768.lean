import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11072 = true := by
  decide +kernel

theorem tot11072 : totK PD2M8K2 D2M8K2.t11072 = [0, 182644712689, 468328298982, 238756720080, 13845291295, 0, 0, 0] := by
  decide +kernel

theorem rows11073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11073 = true := by
  decide +kernel

theorem tot11073 : totK PD2M8K2 D2M8K2.t11073 = [0, 218191594285, 482647088430, 181514091173, 5086124964, 0, 0, 0] := by
  decide +kernel

theorem rows11074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11074 = true := by
  decide +kernel

theorem tot11074 : totK PD2M8K2 D2M8K2.t11074 = [0, 170956882869, 455443351543, 248138204305, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows11075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11075 = true := by
  decide +kernel

theorem tot11075 : totK PD2M8K2 D2M8K2.t11075 = [0, 103120818418, 423068922146, 316203876117, 28503049896, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

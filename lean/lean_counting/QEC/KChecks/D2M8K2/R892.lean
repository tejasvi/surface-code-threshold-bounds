import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3568 = true := by
  decide +kernel

theorem tot3568 : totK PD2M8K2 D2M8K2.t3568 = [0, 186587361691, 473156749022, 222395015444, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows3569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3569 = true := by
  decide +kernel

theorem tot3569 : totK PD2M8K2 D2M8K2.t3569 = [0, 169782633852, 463220369182, 232009690406, 13419997576, 0, 0, 0] := by
  decide +kernel

theorem rows3570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3570 = true := by
  decide +kernel

theorem tot3570 : totK PD2M8K2 D2M8K2.t3570 = [0, 180068682636, 482113639578, 235560925620, 11029064239, 0, 0, 0] := by
  decide +kernel

theorem rows3571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3571 = true := by
  decide +kernel

theorem tot3571 : totK PD2M8K2 D2M8K2.t3571 = [0, 206817259901, 470475694045, 197018485521, 7902352020, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

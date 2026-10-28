import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t696 = true := by
  decide +kernel

theorem tot696 : totK PD2M8K2 D2M8K2.t696 = [0, 196015487751, 500623111318, 203233927815, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t697 = true := by
  decide +kernel

theorem tot697 : totK PD2M8K2 D2M8K2.t697 = [165226116396, 394675492133, 258321380492, 76443340374, 5548806221, 0, 0, 0] := by
  decide +kernel

theorem rows698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t698 = true := by
  decide +kernel

theorem tot698 : totK PD2M8K2 D2M8K2.t698 = [157454563170, 473267969643, 257298596523, 13763488033, 0, 0, 0, 0] := by
  decide +kernel

theorem rows699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t699 = true := by
  decide +kernel

theorem tot699 : totK PD2M8K2 D2M8K2.t699 = [0, 199985762492, 482260075397, 184025213647, 9587713104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

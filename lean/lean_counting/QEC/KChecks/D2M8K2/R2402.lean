import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9608 = true := by
  decide +kernel

theorem tot9608 : totK PD2M8K2 D2M8K2.t9608 = [0, 0, 302410298885, 490852438427, 88265305102, 1107157161, 0, 0] := by
  decide +kernel

theorem rows9609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9609 = true := by
  decide +kernel

theorem tot9609 : totK PD2M8K2 D2M8K2.t9609 = [0, 86757284321, 338176030906, 350912395531, 93645802356, 3824247485, 0, 0] := by
  decide +kernel

theorem rows9610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9610 = true := by
  decide +kernel

theorem tot9610 : totK PD2M8K2 D2M8K2.t9610 = [0, 177025056003, 463037945186, 261037507738, 21084821801, 0, 0, 0] := by
  decide +kernel

theorem rows9611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9611 = true := by
  decide +kernel

theorem tot9611 : totK PD2M8K2 D2M8K2.t9611 = [0, 181687999219, 474042469221, 245177941061, 12057035230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

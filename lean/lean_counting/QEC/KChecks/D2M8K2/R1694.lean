import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6776 = true := by
  decide +kernel

theorem tot6776 : totK PD2M8K2 D2M8K2.t6776 = [0, 222161302067, 490476318459, 173244113924, 4961529011, 0, 0, 0] := by
  decide +kernel

theorem rows6777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6777 = true := by
  decide +kernel

theorem tot6777 : totK PD2M8K2 D2M8K2.t6777 = [0, 186006093263, 460251838999, 223338682647, 17066492788, 0, 0, 0] := by
  decide +kernel

theorem rows6778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6778 = true := by
  decide +kernel

theorem tot6778 : totK PD2M8K2 D2M8K2.t6778 = [0, 164432040207, 444220222963, 281003125844, 28472831638, 0, 0, 0] := by
  decide +kernel

theorem rows6779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6779 = true := by
  decide +kernel

theorem tot6779 : totK PD2M8K2 D2M8K2.t6779 = [0, 197728933841, 486547680056, 215955350562, 8778112492, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

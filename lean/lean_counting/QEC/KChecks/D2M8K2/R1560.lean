import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6240 = true := by
  decide +kernel

theorem tot6240 : totK PD2M8K2 D2M8K2.t6240 = [173043034316, 444235037054, 250383436820, 41287883027, 4412989545, 0, 0, 0] := by
  decide +kernel

theorem rows6241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6241 = true := by
  decide +kernel

theorem tot6241 : totK PD2M8K2 D2M8K2.t6241 = [193570030124, 467503660697, 228246283242, 15422833671, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6242 = true := by
  decide +kernel

theorem tot6242 : totK PD2M8K2 D2M8K2.t6242 = [55817160339, 333551889367, 416129338578, 88990871797, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6243 = true := by
  decide +kernel

theorem tot6243 : totK PD2M8K2 D2M8K2.t6243 = [0, 195805569664, 479766353103, 190379239866, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

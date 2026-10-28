import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4196 = true := by
  decide +kernel

theorem tot4196 : totK PA10K2 A10K2.t4196 = [0, 306467343696, 1529117172431, 2058882858793, 723353049023, 58034192007, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4197 = true := by
  decide +kernel

theorem tot4197 : totK PA10K2 A10K2.t4197 = [0, 315590801309, 1230632203528, 1842352899047, 1080393600773, 213642913445, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4198 = true := by
  decide +kernel

theorem tot4198 : totK PA10K2 A10K2.t4198 = [0, 451790042216, 1767477801620, 2005264193260, 568564747387, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4199 = true := by
  decide +kernel

theorem tot4199 : totK PA10K2 A10K2.t4199 = [0, 66055586215, 793446666034, 1960524769003, 1483222805596, 350976397785, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

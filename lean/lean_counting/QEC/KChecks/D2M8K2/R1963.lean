import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7852 = true := by
  decide +kernel

theorem tot7852 : totK PD2M8K2 D2M8K2.t7852 = [0, 0, 235779856216, 458547700627, 201437979869, 21141756247, 0, 0] := by
  decide +kernel

theorem rows7853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7853 = true := by
  decide +kernel

theorem tot7853 : totK PD2M8K2 D2M8K2.t7853 = [0, 0, 161855308939, 476552714895, 243068163596, 9401650850, 0, 0] := by
  decide +kernel

theorem rows7854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7854 = true := by
  decide +kernel

theorem tot7854 : totK PD2M8K2 D2M8K2.t7854 = [0, 139159530516, 357430492358, 300181789231, 109357565771, 5356395648, 0, 0] := by
  decide +kernel

theorem rows7855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7855 = true := by
  decide +kernel

theorem tot7855 : totK PD2M8K2 D2M8K2.t7855 = [0, 165447102151, 447231547662, 280036755790, 30179797769, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

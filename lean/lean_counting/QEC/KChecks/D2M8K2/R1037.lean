import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4148 = true := by
  decide +kernel

theorem tot4148 : totK PD2M8K2 D2M8K2.t4148 = [0, 0, 58324834770, 408303541920, 370741712152, 31526808811, 0, 0] := by
  decide +kernel

theorem rows4149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4149 = true := by
  decide +kernel

theorem tot4149 : totK PD2M8K2 D2M8K2.t4149 = [0, 0, 156487630423, 413937528880, 310429541624, 36942824933, 0, 0] := by
  decide +kernel

theorem rows4150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4150 = true := by
  decide +kernel

theorem tot4150 : totK PD2M8K2 D2M8K2.t4150 = [0, 0, 196118405424, 474603375485, 212667913924, 14633607569, 0, 0] := by
  decide +kernel

theorem rows4151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4151 = true := by
  decide +kernel

theorem tot4151 : totK PD2M8K2 D2M8K2.t4151 = [0, 0, 149024447220, 480710346158, 241746999104, 11068810259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

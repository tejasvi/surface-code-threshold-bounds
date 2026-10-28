import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15668 = true := by
  decide +kernel

theorem tot15668 : totK PD2M8K2 D2M8K2.t15668 = [0, 0, 89289124153, 368821322822, 371522188533, 61031020222, 1107157161, 0] := by
  decide +kernel

theorem rows15669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15669 = true := by
  decide +kernel

theorem tot15669 : totK PD2M8K2 D2M8K2.t15669 = [0, 0, 29317429062, 289087849118, 459807736006, 116263021818, 3824247485, 0] := by
  decide +kernel

theorem rows15670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15670 = true := by
  decide +kernel

theorem tot15670 : totK PD2M8K2 D2M8K2.t15670 = [0, 0, 178977194272, 466611056382, 245757313301, 20104258212, 0, 0] := by
  decide +kernel

theorem rows15671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15671 = true := by
  decide +kernel

theorem tot15671 : totK PD2M8K2 D2M8K2.t15671 = [0, 0, 191804543919, 476464280634, 228996643335, 12524139187, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

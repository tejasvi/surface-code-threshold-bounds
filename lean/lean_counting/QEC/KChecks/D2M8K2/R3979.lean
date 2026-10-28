import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15916 = true := by
  decide +kernel

theorem tot15916 : totK PD2M8K2 D2M8K2.t15916 = [0, 153525330889, 460360715090, 256268763377, 16426728340, 0, 0, 0] := by
  decide +kernel

theorem rows15917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15917 = true := by
  decide +kernel

theorem tot15917 : totK PD2M8K2 D2M8K2.t15917 = [0, 0, 278359273999, 503594632839, 109237343448, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15918 = true := by
  decide +kernel

theorem tot15918 : totK PD2M8K2 D2M8K2.t15918 = [0, 93030726523, 384279325022, 387947696915, 52069366991, 0, 0, 0] := by
  decide +kernel

theorem rows15919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15919 = true := by
  decide +kernel

theorem tot15919 : totK PD2M8K2 D2M8K2.t15919 = [0, 172869004024, 456635767272, 262858320992, 21150741485, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
